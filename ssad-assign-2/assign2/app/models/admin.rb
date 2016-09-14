class Admin < ApplicationRecord
    validates :username, presence: true, uniqueness: true
    validates :password, presence: true, length: {minimum: 1}
   
    def authenticate(given_password)
        return self.password == given_password
    end
end
