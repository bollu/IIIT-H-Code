class Question < ApplicationRecord
    attr_accessor :survey_name

    validates :question, presence: true, length: {minimum: 1} 
    belongs_to :survey 
end
