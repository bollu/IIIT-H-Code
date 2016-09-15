class UserSurveyAnswerStatus < ApplicationRecord
    has_one: user
    has_one: survey
    has_many: answer
    
    validates :answered, presence: true 
end
